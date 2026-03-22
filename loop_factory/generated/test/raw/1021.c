int main1(){
  int j, xm, bf2l, e;

  j=(1%35)+9;
  xm=0;
  bf2l=j;
  e=j;

  while (1) {
      if (!(xm<=j-1)) {
          break;
      }
      bf2l = bf2l + 5;
      e += bf2l;
      xm++;
  }

}
