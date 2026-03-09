int main1(int w){
  int fsy, jl, y07, rrw, o02h;

  fsy=w+12;
  jl=0;
  y07=1;
  rrw=0;
  o02h=jl;

  while (1) {
      if (!(y07<=fsy)) {
          break;
      }
      rrw = rrw+2*y07-1;
      y07 += 1;
      w = w + 3;
      o02h += y07;
  }

}
