int main1(int b,int s){
  int zcw, i9, h;

  zcw=(b%26)+5;
  i9=0;
  h=zcw;

  while (1) {
      if (!(i9<zcw&&h>0)) {
          break;
      }
      i9 = i9 + 1;
      h = h - 1;
      s += h;
      b += 1;
  }

}
