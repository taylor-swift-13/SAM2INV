int main191(int r,int s){
  int ab, z, of, y, o, c, sc6, cy;

  ab=48;
  z=1;
  of=0;
  y=0;
  o=0;
  c=0;
  sc6=0;
  cy=s;

  while (of<ab) {
      if (of%8==0) {
          sc6++;
      }
      else {
          if (of%6==0) {
              c = c + 1;
          }
          else {
              if (of%7==0) {
                  o = o + 1;
              }
              else {
                  y++;
              }
          }
      }
      of = of + 1;
      r = (r+of)%6;
  }

  while (1) {
      if (!(sc6<=z-1)) {
          break;
      }
      cy++;
      r = r+z-sc6;
      s++;
      of += cy;
  }

}
