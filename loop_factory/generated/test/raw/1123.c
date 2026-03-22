int main1(){
  int lg, u, w, h, vg;

  lg=1*2;
  u=1;
  w=1*2;
  h=2;
  vg=-6;

  while (u*2<=lg) {
      h = h + w;
      w = w + u;
      lg = (u*2)-1;
  }

  while (vg<lg) {
      vg += 1;
      w += 1;
      h = h + u;
  }

}
