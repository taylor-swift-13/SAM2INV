int main81(int x,int z){
  int bmm, cg, c8vt, wh, c407;

  bmm=z*2;
  cg=0;
  c8vt=-8;
  wh=2;
  c407=bmm;

  while (1) {
      if (cg>=bmm) {
          break;
      }
      cg++;
      c8vt += 1;
      wh = wh+(c8vt%4);
      c407 = c407 + 3;
      x = x+bmm-cg;
      z = z+(c8vt%6);
  }

}
