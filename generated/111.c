int main111(int p,int u,int t){
  int lu, jxjt, sz, azd, li3r, w, vq;

  lu=t;
  jxjt=0;
  sz=0;
  azd=0;
  li3r=5;
  w=jxjt;
  vq=lu;

  while (1) {
      if (!(sz<lu&&li3r>0)) {
          break;
      }
      azd += li3r;
      sz = sz + 1;
      w += jxjt;
      li3r--;
      p = p+(li3r%6);
      vq = vq+(li3r%3);
  }

}
