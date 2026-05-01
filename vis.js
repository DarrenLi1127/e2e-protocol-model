{
    // 清空画布
    d3.select(svg).selectAll("*").remove();
    const inst = instances[currentInstance];

    // 缩减总宽度，确保在窄屏幕下也能看全
    const myWidth = 720; 
    const myHeight = 500;
    
    const svgCanvas = d3.select(svg)
        .attr("width", myWidth)
        .attr("height", myHeight)
        .style("background-color", "#f8f9fa")
        .style("border-radius", "10px");

    // 标题
    svgCanvas.append("text")
        .attr("x", 20).attr("y", 30)
        .attr("font-family", "sans-serif").attr("font-size", "16px").attr("font-weight", "bold")
        .text(`State ${currentInstance}`);

    const positions = {
        "Alice0": { x: 30,  y: 60,  color: "#e3f2fd", border: "#2196f3" },
        "Bob0":   { x: 30,  y: 280, color: "#e8f5e9", border: "#4caf50" },
        "Eve0":   { x: 380, y: 170, color: "#ffebee", border: "#f44336" } // Eve 向左移动了 70px
    };

    // 提取关系数据
    const knowsRel = inst.field("knows").tuples();
    const privRel = inst.field("current_priv").tuples();
    const pubRel = inst.field("last_other_pub").tuples();
    const ratchetRel = inst.field("needs_ratchet").tuples();

    Object.keys(positions).forEach(nodeId => {
        const pos = positions[nodeId];
        const boxWidth = 240; // 宽度从 300 缩小到 240
        const boxHeight = 180;
        
        // 1. 绘制主体框
        svgCanvas.append("rect")
            .attr("x", pos.x).attr("y", pos.y)
            .attr("width", boxWidth).attr("height", boxHeight)
            .attr("rx", 10).attr("fill", pos.color).attr("stroke", pos.border).attr("stroke-width", 2);

        // 2. 角色名称
        svgCanvas.append("text")
            .attr("x", pos.x + 12).attr("y", pos.y + 25)
            .attr("font-family", "sans-serif").attr("font-size", "15px").attr("font-weight", "bold")
            .attr("fill", pos.border).text(nodeId.replace("0", ""));

        // 3. 状态面板 (Status Panel)
        const getVal = (rel) => {
            const entry = rel.find(t => t.atoms()[0].id() === nodeId);
            return entry ? entry.atoms()[1].id().replace("0", "") : "None";
        };

        const statusX = pos.x + 12;
        const statusY = pos.y + 45;
        
        const states = [
            { label: "Priv:", val: getVal(privRel) },
            { label: "Pub:", val: getVal(pubRel) },
            { label: "Ratchet:", val: getVal(ratchetRel) }
        ];

        states.forEach((s, i) => {
            const rowY = statusY + i * 16;
            svgCanvas.append("text")
                .attr("x", statusX).attr("y", rowY)
                .attr("font-family", "monospace").attr("font-size", "10px").attr("fill", "#555")
                .text(`${s.label} ${s.val}`);
        });

        // 4. 密钥库 (Knowledge Base) - 调整为两列排列以节省宽度
        svgCanvas.append("text")
            .attr("x", statusX).attr("y", statusY + 60)
            .attr("font-family", "sans-serif").attr("font-size", "11px").attr("font-weight", "bold")
            .attr("fill", "#333").text("Knowledge Base:");

        const nodeKeys = knowsRel.filter(t => t.atoms()[0].id() === nodeId).map(t => t.atoms()[1].id());
        
        nodeKeys.forEach((key, i) => {
            const isAES = key === "Key8" || key.includes("AES");
            const col = i % 2; // 改为 2 列
            const row = Math.floor(i / 2);
            const tagX = statusX + col * 110;
            const tagY = statusY + 70 + row * 20;

            svgCanvas.append("rect")
                .attr("x", tagX).attr("y", tagY)
                .attr("width", 100).attr("height", 16).attr("rx", 4)
                .attr("fill", isAES ? "#f1c40f" : "#fff").attr("stroke", "#ccc");

            svgCanvas.append("text")
                .attr("x", tagX + 50).attr("y", tagY + 12)
                .attr("text-anchor", "middle").attr("font-family", "monospace")
                .attr("font-size", "9px").attr("font-weight", isAES ? "bold" : "normal")
                .text(key);
        });
    });

    const lineData = [
        [270, 150], // Alice 框右侧
        [380, 260], // Eve 框左侧
        [270, 370]  // Bob 框右侧
    ];

    const lineGenerator = d3.line();
    svgCanvas.append("path")
        .attr("d", lineGenerator(lineData))
        .attr("fill", "none").attr("stroke", "#e74c3c").attr("stroke-width", 1.5)
        .attr("stroke-dasharray", "4,4");

    svgCanvas.append("text")
        .attr("x", 300).attr("y", 255).attr("fill", "#e74c3c")
        .attr("font-family", "sans-serif").attr("font-size", "10px").attr("font-weight", "bold")
        .text("MITM ⚡️");
}