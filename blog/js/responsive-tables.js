const tables = document.querySelectorAll('.content table');
for (let i = 0; i < tables.length; i++) {
  const table = tables[i];
  const wrapper = document.createElement('div');
  wrapper.className = 'table-wrapper';
  table.parentElement.replaceChild(wrapper, table);
  wrapper.appendChild(table);
}