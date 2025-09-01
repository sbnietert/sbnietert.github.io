document.querySelectorAll('.bib-copy').forEach(button => {
  button.addEventListener('click', () => {
    const pre = button.nextElementSibling; // get the <pre> block
    navigator.clipboard.writeText(pre.textContent)
      .then(() => { button.textContent = 'Copied!'; setTimeout(() => button.textContent = 'Copy', 1000); })
      .catch(err => console.error('Copy failed', err));
  });
});