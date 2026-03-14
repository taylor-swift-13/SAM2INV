int main1(){
  int y, i, l, mo, e8, dnba;

  y=1+9;
  i=y+5;
  l=0;
  mo=0;
  e8=7;
  dnba=i;

  while (mo<=y-1) {
      e8 = e8*4;
      dnba = dnba + i;
      mo++;
      l = l + 1;
  }

  while (1) {
      if (!(y+1<=i)) {
          break;
      }
      if (y%2==0) {
          e8 += l;
      }
      else {
          e8 = e8+l+1;
      }
      i = (y+1)-1;
  }

}
