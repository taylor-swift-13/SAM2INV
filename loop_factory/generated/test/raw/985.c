int main1(){
  int s1, yzr, si, y, a2b, sz;

  s1=1+17;
  yzr=0;
  si=0;
  y=0;
  a2b=0;
  sz=0;

  while (yzr<s1) {
      if (!(!(yzr%11==0))) {
          if (yzr%8==0) {
              a2b += 1;
          }
          else {
              if (yzr%3==0) {
                  y++;
              }
              else {
                  si++;
              }
          }
      }
      else {
          sz = sz + 1;
      }
      yzr = yzr + 1;
      y = y + a2b;
  }

}
