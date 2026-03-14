int main1(int j){
  int w, kk, i2, b, o6m, vhj;

  w=j+19;
  kk=0;
  i2=0;
  b=0;
  o6m=kk;
  vhj=w;

  while (1) {
      if (!(b<w)) {
          break;
      }
      b += 1;
      i2 += j;
      o6m += 2;
      vhj = vhj+(b%6);
  }

  while (o6m+3<=i2) {
      b = b + w;
      vhj += b;
      w += 2;
      i2 = (o6m+3)-1;
  }

}
