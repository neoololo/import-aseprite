import { Struct } from 'typed-struct';
import * as fs from "fs";
import * as zlib from "zlib";
import sharp from "sharp";
import pack from "bin-pack";
import crc from "crc/crc32";
import path from 'path';

const charset = '0123456789abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ';
const randstring = (n: number) => [...new Array(n)].map(e => charset[~~(Math.random() * charset.length)]).join('');

const headerParser = new Struct('ASEHeader')
    .UInt32LE('size')
    .UInt16LE('magic')
    .UInt16LE('frame_count')
    .UInt16LE('width')
    .UInt16LE('height')
    .UInt16LE('depth')
    .UInt32LE('flags')
    .UInt16LE('speed_deprecated')
    .UInt16LE('zero_0')
    .UInt16LE('zero_1')
    .UInt8('transparent_palette_index')
    .UInt8Array('ign', 3)
    .UInt16LE('color_number')
    .UInt8('pixel_width')
    .UInt8('pixel_height')
    .Int16LE('grid_x')
    .Int16LE('grid_w')
    .UInt16LE('grid_width')
    .UInt16LE('grid_height')
    .UInt8Array('_reserved', 84)
    .compile();

const frameParser = new Struct('ASEFrame')
    .UInt32LE('size')
    .UInt16LE('magic')
    .UInt16LE('chunk_count_old')
    .UInt16LE('frame_duration')
    .UInt8Array('_reserved', 2)
    .UInt16LE('chunk_count')
    .compile();

type AseOldPaletteChunk = {
    type: 0x0004;
    table: [number, number, number][];
};

type AseOldPaletteChunk2 = { type: 0x0011; };
type AsePaletteChunk = { type: 0x2019; };

enum ColorProfileType {
    NoColorProfile,
    sRGB,
    EmbeddedICC
}
type AseColorProfileChunk = {
    type: 0x2007,
    color_type: ColorProfileType;
    specialFixedGamma: boolean;
    gamma: number;
    icc_profile?: any;
};

type AseLayerChunk = {
    type: 0x2004;
    data: {
        visible: boolean,
        editable: boolean,
        lock: boolean, background: boolean, prefer_linked: boolean, collapsed: boolean, reference: boolean,
        layer_type: number, child_level: number,
        default_width: number,
        default_height: number,
        blend_mode: number,
        opacity: number,
        name: string;
    };
};

type AseUserData = {
    type: 0x2020;
    text?: string;
    color?: number[];
    prop?: Record<string, any>;
};

type AseChunk = (AseCelChunk | AseLayerChunk | AseTagsChunk | AseColorProfileChunk | AseOldPaletteChunk | AseOldPaletteChunk2 | AsePaletteChunk) & { userdata?: AseUserData[]; };

type AseFrame = {
    duration: number;
    chunks: AseChunk[];
};

const parseColorProfile = (buffer: Buffer): AseColorProfileChunk => {
    const cp = buffer.readUint16LE(0);
    const flags = buffer.readUint16LE(0);

    return {
        type: 0x2007,
        color_type: cp as ColorProfileType,
        gamma: 0, // 2lazy2parse fixed point
        specialFixedGamma: (flags & 1) == 1
    };
};

const parseOldPalette = (buffer: Buffer): AseOldPaletteChunk => {
    let ptr = 0;
    const packet_number = buffer.readUint16LE(ptr);
    ptr += 2;
    let table: AseOldPaletteChunk['table'] = [];
    for (let i = 0; i < packet_number; ++i) {
        let skip = buffer[ptr];
        const entries_count = buffer[ptr + 1] || 256;
        for (let j = 0; j < entries_count; ++j, ptr += 3) {
            if (skip-- > 0)
                continue;
            table.push([buffer[ptr + 0], buffer[ptr + 1], buffer[ptr + 2]]);
        }
        ptr += 2;
    }

    return {
        type: 4,
        table
    };
};

const aseLayerChunkParser = new Struct('ASELayerData')
    .Bits16({ visible: [0, 1], editable: [1, 1], lock: [2, 1], background: [3, 1], prefer_linked: [4, 1], collapsed: [5, 1], reference: [6, 1] })
    .UInt16LE('layer_type')
    .UInt16LE('child_level')
    .UInt16LE('default_width')
    .UInt16LE('default_height')
    .UInt16LE('blend_mode')
    .UInt8('opacity')
    .UInt8Array('_reserved', 3)
    .String('name')
    .compile();// ignored: tileset index

const readCstring = (b: Buffer, off: number = 0, end = b.byteLength) => {
    let s = '';
    while (off < end && b[off] !== 0) {
        s += String.fromCharCode(b[off]);
        off++;
    }
    return s;
};

const readPstring = (b: Buffer, off: number = 0) => b.subarray(off + 2, off + 2 + b.readInt16LE(off)).toString();

const parseLayer = (buffer: Buffer): AseLayerChunk => {
    const flags = buffer.readUint16LE(0);

    const data = {
        visible: 0 != (flags & 1),
        editable: 0 != (flags & 2),
        lock: 0 != (flags & 4),
        background: 0 != (flags & 8),
        prefer_linked: 0 != (flags & 16),
        collapsed: 0 != (flags & 32),
        reference: 0 != (flags & 64),
        layer_type: 0, child_level: 0,
        default_width: 0,
        default_height: 0,
        blend_mode: 0,
        opacity: 255,
        name: readPstring(buffer, 16) // documentation says it's offset 14, though!?!?
    };

    return {
        type: 0x2004,
        data
    };
};

type AseTagsChunk = {
    type: 0x2018,
    tags: { from: number, to: number, loop_type: number, repeat: number, color: number[], name: string; }[];
};

const parseTagsChunk = (b: Buffer): AseTagsChunk => {
    let ptr = 0;
    let tag_count = b.readInt16LE(ptr);
    ptr += 10;
    let tags: { from: number, to: number, loop_type: number, repeat: number, color: number[], name: string; }[] = [];
    for (let i = 0; i < tag_count; ++i) {
        const from = b.readInt16LE(ptr + 0);
        const to = b.readInt16LE(ptr + 2);
        const loop_type = b[ptr + 4];
        const repeat = b.readInt16LE(ptr + 5);
        ptr += 7;
        ptr += 6;
        // ptr = 12
        const color = [b[ptr + 0], b[ptr + 1], b[ptr + 2]];
        ptr += 3;
        ptr += 1;
        const name = readPstring(b, ptr);
        tags.push({
            from, to, loop_type, repeat, color, name
        });
        ptr += name.length + 2;
    };
    return {
        type: 0x2018,
        tags
    };
};

const parseUserData = (b: Buffer): AseUserData => {
    let text: string | undefined;
    let ptr = 0;
    const flags = b.readUint32LE();
    ptr += 4;
    if (flags & 1) {
        text = readPstring(b, ptr);
        ptr += 2 + text.length;
    }
    let color: number[] | undefined;
    if (flags & 2) {
        color = [...b.subarray(ptr, ptr + 4)];
    }

    // dont parse properties

    return {
        type: 0x2020,
        text, color
    };
};

type AseCelChunk = {
    type: 0x2005;
    layeridx: number;
    x: number;
    y: number;
    opacity: number;
    zindex: number;
} & ({
    celtype: 0;
    width: number;
    height: number;
    pixels: Buffer;
} | {
    celtype: 1;
    width: number;
    height: number;
    pixels: Buffer;
} | {
    celtype: 2;
    width: number;
    height: number;
    pixels: Buffer;
} | {
    celtype: 3;
    width: number;
    height: number;
    pixels: Buffer;
});

const parseCel = (b: Buffer, previousFrames: AseFrame[]): AseCelChunk => {
    const layeridx = b.readUint16LE(0);
    const x = b.readInt16LE(2);
    const y = b.readInt16LE(4);
    const opacity = b[6];
    const celtype = b.readInt16LE(7);
    const zindex = b.readInt16LE(9);
    // 5 zero bytes
    const rest = b.subarray(16);
    switch (celtype) {
        case 0:
            return {
                type: 0x2005,
                layeridx, x, y, opacity, zindex,
                width: rest.readUint16LE(0),
                height: rest.readUint16LE(2),
                pixels: rest.subarray(4),
                celtype,
            };
        case 1:
            const originFrame = previousFrames[rest.readUint16LE(0)];
            const originCell = originFrame.chunks.find(e => e.type == 0x2005 && e.layeridx == layeridx) as AseCelChunk;

            return {
                type: 0x2005,
                celtype: 1,
                layeridx,
                opacity,
                zindex,
                y: originCell.y,
                x: originCell.x,
                pixels: originCell.pixels,
                height: originCell.height,
                width: originCell.width
            };
        case 2:
            const ret = {
                type: 0x2005,
                layeridx, x, y, opacity, zindex,
                width: rest.readUint16LE(0),
                height: rest.readUint16LE(2),
                pixels: zlib.inflateSync(rest.subarray(4)),
                celtype,
            };
            return ret as any;
        default:
            throw new Error("Unsupported cel type");
    }
};

const parseFile = (buffer: Buffer) => {
    const header = new headerParser(buffer.subarray(0, 128));
    if (header.color_number == 0)
        header.color_number = 256;
    let ptr = 128;
    let frames: AseFrame[] = [];
    const seentypes = new Set<number>();
    for (let i = 0; i < header.frame_count; ++i) {
        const sl = buffer.subarray(ptr, ptr + 16);
        const frame = new frameParser(sl);
        if (frame.chunk_count == 0)
            frame.chunk_count = frame.chunk_count_old;

        ptr += 16;
        let chunks: AseChunk[] = [];
        let pchunk: AseChunk | undefined;
        for (let j = 0; j < frame.chunk_count; ++j) {
            const chunksize = buffer.readUint32LE(ptr);
            const chunk_type = buffer.readUint16LE(ptr + 4);
            const data = buffer.subarray(ptr + 6, ptr + chunksize);
            let chunk: AseChunk;
            let upd = true;

            switch (chunk_type) {
                case 0x0004:
                    chunk = parseOldPalette(data);
                    break;
                case 0x2004:
                    chunk = parseLayer(data);
                    break;
                case 0x2005:
                    chunk = parseCel(data, frames);
                    break;
                case 0x2007:
                    chunk = parseColorProfile(data);
                    break;
                case 0x2018: // can only appear once
                    chunk = parseTagsChunk(data);
                    break;
                case 0x2020:
                    upd = false;
                    if (pchunk) {
                        pchunk.userdata ||= [];
                        const ud = parseUserData(data);
                        pchunk.userdata.push(ud);
                    }
                    ptr += chunksize;
                    continue;
                default:
                    ptr += chunksize;
                    seentypes.add(chunk_type);
                    continue;
            }
            chunks.push(chunk);
            if (upd)
                pchunk = chunk;
            ptr += chunksize;
        }
        frames.push({ duration: frame.frame_duration, chunks });
    }

    return {
        header,
        frames,
        types: [...seentypes].map(e => e.toString(16))
    };
};

const emptybuffer = Buffer.alloc(0);

export const doGeneration = (modname: string, file: Buffer, js = false, sheet = false, animdata = false) => {
    const parsed = parseFile(file);
    const layers = parsed.frames.flatMap(e => e.chunks.filter(e => e.type == 0x2004)) as (AseLayerChunk & { userdata?: AseUserData[]; })[];
    const usedlayers = layers.filter(l => l.userdata?.length);
    let layerid = usedlayers.map(e => layers.indexOf(e));

    const cells = parsed.frames.flatMap(e => {
        let ret = e.chunks.filter(t => t.type == 0x2005).map(e => (e as AseCelChunk));
        // add empty cels for each layer in the frame that doesn't have a real cel
        let remaining_ids = new Set(layers.map((e, i) => i))
        ret.forEach(r => remaining_ids.delete(r.layeridx));
        // only keep ids of layers that are used
        for (let r of remaining_ids)
            if (!layerid.includes(r))
                remaining_ids.delete(r);
        // empty cel
        return ret.concat([...remaining_ids].map(lid => ({
            type: 0x2005,
            layeridx: lid,
            zindex: 0, // unused
            opacity: 255,
            celtype: 0,
            x: 0, y: 0,
            width: 0, height: 0,
            pixels: emptybuffer
        } as AseCelChunk)))
    });

    // bogus crc-based cel dedup
    const crcs = cells.map(e => crc(e.pixels));
    const added = new Set<AseCelChunk>();
    const addedc = new Set<number>();
    const crc2uniqcell = new Map<number, AseCelChunk>();
    cells.filter((c, i) => {
        if (addedc.has(crcs[i]))
            return false;
        addedc.add(crcs[i]);
        added.add(c);
        crc2uniqcell.set(crcs[i], c);
        return true;
    });

    const animflags = new Set(usedlayers.flatMap(e => e.userdata?.flatMap(e => e.text?.split('&'))).filter(e => e) as string[]);
    const uniquecells = [...added].filter(c => c.width && layers[c.layeridx].userdata);
    const res2 = pack(uniquecells);

    let spritesheetdata: Promise<Buffer> | undefined;
    const celtoitem = new Map<AseCelChunk, typeof res2.items[number]>();

    if (sheet) {
        const spritesheet = Buffer.alloc(res2.width * res2.height * 4);

        const blitSpriteSheet = (src: Buffer, sw: number, sh: number, dx: number, dy: number) => {
            for (let j = 0; j < sh; ++j) {
                for (let i = 0; i < sw; ++i) {
                    const dptr = ((j + dy) * res2.width + (i + dx)) * 4;
                    const sptr = (j * sw + i) * 4;
                    for (let k = 0; k < 4; ++k)
                        spritesheet[dptr + k] = src[sptr + k];
                }
            }
        };

        for (let i of res2.items) {
            const cel = i.item;
            celtoitem.set(cel, i);
            const bounds = i;
            if (cel.width && cel.height)
                blitSpriteSheet(cel.pixels, cel.width, cel.height, bounds.x, bounds.y);
        }

        const img = sharp(spritesheet, { raw: { width: res2.width, height: res2.height, channels: 4 } });
        spritesheetdata = img.png().toBuffer();
    } else {
        for (let i of res2.items) {
            const cel = i.item;
            celtoitem.set(cel, i);
        }
    }

    let arr = new Int16Array(6 * usedlayers.length * parsed.header.frame_count);
    let ptr = 0;

    let flags = Object.fromEntries([...animflags].map((e, i) => [e, i]));

    const computeFlags = (n: string) => {
        const uniques = n.split('&').map(e => e.trim());
        let ret = 0;
        for (const u of uniques)
            if (u in flags)
                ret |= 1 << flags[u];
        return ret;
    };

    let layermeta = [];
    let writtencells = 0;
    // writes, layer by layer, the coordinates
    for (let l of usedlayers) {
        let wl = 0;
        if (animdata) {
            for (let c = 0; c < cells.length; ++c) {
                const cel = cells[c];
                if (cel.layeridx != layerid[0])
                    continue;
                const crcofc = crcs[c];
                const uniqcel = crc2uniqcell.get(crcofc);
                if (!uniqcel)
                    throw new Error("Wtf");
                if (!cel.width) {
                    arr[ptr++] = 0;
                    arr[ptr++] = 0;
                    arr[ptr++] = 0;
                    arr[ptr++] = 0;
                    arr[ptr++] = 0;
                    arr[ptr++] = 0;
                } else {
                    const zone = celtoitem.get(uniqcel);
                    if (!zone)
                        throw new Error("Wtf2");
                    arr[ptr++] = cel.x;
                    arr[ptr++] = cel.y;
                    arr[ptr++] = cel.width;
                    arr[ptr++] = cel.height;
                    arr[ptr++] = zone.x;
                    arr[ptr++] = zone.y;
                }
                writtencells++;
                wl++;
            }
        }
        layermeta.push(computeFlags(l.userdata![0].text!));
        layerid.shift()
    }

    const tags = parsed.frames.flatMap(e => e.chunks).find(e => e.type == 0x2018) as AseTagsChunk;

    const retagged = Object.fromEntries(tags.tags.map(e => [e.name,
    [e.from, e.to, e.loop_type, e.repeat] as [from: number, to: number, loop_type: number, repeat: number]
    ]));

    const module = modname.replace('.aseprite', '');
    const code = (`
import spritesheet from "./${module}-ss.png";
import animdata from "./${module}-anim.bin";
    
export default {
    spritesheet,
    animdata,
    extent: ${JSON.stringify([parsed.header.width, parsed.header.height])} as const,
    frame_count: ${parsed.header.frame_count} as const,
    anims: ${JSON.stringify(retagged)} as const,
    flags: ${JSON.stringify(flags)} as const,
    layers_props: ${JSON.stringify(layermeta)} as const,
    frame_durations: ${JSON.stringify(parsed.frames.map(f => f.duration))} as const
}`);

    return {
        code: js ? code.replaceAll(' as const', '') : code,
        spritesheet: spritesheetdata,
        animdata: animdata ? arr : undefined
    };
};

export default () => {
    let config: any;
    return {
        name: 'aseprite-import',
        configResolved(resolvedConfig: any) {
            // store the resolved config
            config = resolvedConfig;
        },
        enforce: 'pre',

        async load(id: string) {
            if (!id.endsWith('.aseprite'))
                return;
            const modstats = fs.statSync(id);
            const fqn = id.replace('.aseprite', '').replace(config.root + '/', '');
            const { code, spritesheet, animdata } = doGeneration(path.basename(fqn), fs.readFileSync(id), true, true, true);
            const tryWrite = async (target: string, data: Buffer) => {
                try {
                    fs.mkdirSync(path.dirname(target), { recursive: true });
                }
                catch { }
                try {
                    let st = fs.statSync(target);
                    if (st.mtimeMs < modstats.mtimeMs)
                        fs.writeFileSync(target, data);
                } catch {
                    fs.writeFileSync(target, data);
                }
            }
            if (spritesheet) {
                const target = path.resolve(path.dirname(id), `${path.basename(fqn)}-ss.png`);
                await tryWrite(target, await spritesheet);
            }
            if (animdata) {
                const target = path.resolve(path.dirname(id), `${path.basename(fqn)}-anim.bin`);
                await tryWrite(target, Buffer.from(animdata.buffer));
            }
            return code;
        }
    };
};