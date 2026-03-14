int main1(){
  int a, cs, yxo, sy, i, wm0;

  a=1+11;
  cs=0;
  yxo=0;
  sy=0;
  i=0;
  wm0=0;

  while (cs<a) {
      if (!(!(cs%11==0))) {
          if (cs%9==0) {
              i = i + 1;
          }
          else {
              if (cs%6==0) {
                  sy += 1;
              }
              else {
                  yxo++;
              }
          }
      }
      else {
          wm0 = wm0 + 1;
      }
      yxo++;
      cs++;
  }

}
