int main1(int w){
  int i8, t50, t, g8, a, ijh0, df;

  i8=w;
  t50=0;
  t=0;
  g8=0;
  a=0;
  ijh0=0;
  df=0;

  while (1) {
      if (!(t<i8)) {
          break;
      }
      if (t%10==0) {
          df++;
      }
      else {
          if (t%5==0) {
              ijh0 = ijh0 + 1;
          }
          else {
              if (t%7==0) {
                  a++;
              }
              else {
                  g8 = g8 + 1;
              }
          }
      }
      w = w + i8;
      t += 1;
  }

  for (; t-4>=0; t -= 4) {
      w = w + w;
      w = w + t50;
      t50++;
  }

}
