int main1(int a,int f){
  int c, lcl0, u9, fn, s, vw;

  c=26;
  lcl0=0;
  u9=0;
  fn=0;
  s=0;
  vw=0;

  while (lcl0<=c-1) {
      if (!(!(lcl0%7==0))) {
          if (lcl0%5==0) {
              s++;
          }
          else {
              if (lcl0%6==0) {
                  fn += 1;
              }
              else {
                  u9 = u9 + 1;
              }
          }
      }
      else {
          vw = vw + 1;
      }
      lcl0 = lcl0 + 1;
      f = f + vw;
  }

}
