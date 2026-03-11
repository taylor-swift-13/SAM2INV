int main1(){
  int mb1, me1r, b4y, ty, nj7, kw72;

  mb1=1+3;
  me1r=0;
  b4y=0;
  ty=0;
  nj7=mb1;
  kw72=mb1;

  while (ty<=mb1-1) {
      ty = ty + 1;
      b4y++;
      nj7 = nj7 + b4y;
      nj7 = nj7*3;
  }

  while (nj7>kw72) {
      if (nj7%2==0) {
          b4y += mb1;
      }
      else {
          b4y = b4y+mb1+1;
      }
      me1r = me1r + b4y;
      nj7 = kw72;
  }

}
