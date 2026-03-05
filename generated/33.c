int main33(int z,int k){
  int te, u, qhy7, bj, g, c, ul;

  te=k;
  u=0;
  qhy7=k;
  bj=z;
  g=0;
  c=0;
  ul=k;

  while (1) {
      qhy7 = qhy7*2;
      g = g%8;
      bj = bj + qhy7;
      if ((u%6)==0) {
          k = c*c;
      }
      else {
          ul = ul%7;
      }
      u = u + 1;
      if (u>=te) {
          break;
      }
  }

}
