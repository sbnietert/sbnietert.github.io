let socket;
let accel = [];
const width = window.innerWidth,
      height = window.innerHeight;
let ctx;
let lastUpdate;

document.addEventListener('DOMContentLoaded', function() {
  socket = io.connect('http://ec2-52-37-70-181.us-west-2.compute.amazonaws.com:3000');
  lastUpdate = Date.now();
  socket.on('accel update', function(data) {
    accel.push(data);
    if(accel.length > width) {
      accel.shift();
    }
    lastUpdate = Date.now();
  });

  const canvas = document.getElementById('graph');
  canvas.width = width;
  canvas.height = height;
  ctx = canvas.getContext('2d');
  setInterval(update, 1000/30);
});

function plotTimeSeries(data, shift, scale, strokeStyle) {
  if (data.length == 0) return;

  ctx.beginPath();
  let x = 0, y = data[0];
  data.forEach(val => {
    ctx.moveTo(x, y);
    x++;
    y = (val + shift)/scale * height;
    ctx.lineTo(x, y);
  });
  ctx.strokeStyle = strokeStyle;
  ctx.stroke();
  ctx.closePath();
}

function update() {
  ctx.clearRect(0, 0, width, height);

  const accel_x = accel.map(a => a.x);
  const accel_y = accel.map(a => a.y);
  const accel_z = accel.map(a => a.z);

  plotTimeSeries(accel_x, 10, 20, 'red');
  plotTimeSeries(accel_y, 10, 20, 'blue');
  plotTimeSeries(accel_z, 0, 20, 'green');

  const dt = (Date.now() - lastUpdate)/1000;
  ctx.fillText('Time since last update: ' + dt.toFixed(2) + ' seconds', 5, height - 5);
}
