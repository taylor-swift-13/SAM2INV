int main1(){
  int z, k, wd, f3m, ye, oy;

  z=(1%35)+15;
  k=(1%35)+15;
  wd=1;
  f3m=0;
  ye=0;
  oy=1;

  while (1) {
      if (!(z!=k)) {
          break;
      }
      if (z>k) {
          z = z - k;
          wd -= f3m;
          ye -= oy;
      }
      else {
          k -= z;
          f3m = f3m - wd;
          oy -= ye;
      }
      wd = wd*2;
  }

}
