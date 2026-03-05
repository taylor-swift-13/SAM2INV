int main88(int q){
  int e, quv, s, h9zm, md1, xl;

  e=q;
  quv=0;
  s=0;
  h9zm=6;
  md1=20;
  xl=q;

  while (1) {
      if (!(quv<e&&h9zm>0)) {
          break;
      }
      s += h9zm;
      quv = quv + 1;
      md1 = md1+(s%5);
      h9zm = h9zm - 1;
      xl += quv;
      q = q*q+md1;
  }

}
