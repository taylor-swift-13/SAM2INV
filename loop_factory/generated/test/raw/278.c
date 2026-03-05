int main1(int e,int l){
  int yl, f5e, u9x0;

  yl=(e%38)+14;
  f5e=1;
  u9x0=1;

  while (f5e<=yl-2) {
      if (u9x0==1) {
          u9x0 = 2;
      }
      else {
          if (u9x0==2) {
              u9x0 = 1;
          }
      }
      l += u9x0;
      e += 1;
  }

}
