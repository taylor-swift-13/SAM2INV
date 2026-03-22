int main1(){
  int am, l, od, r, ov, y53, di, p, us;

  am=1;
  l=2;
  od=6;
  r=0;
  ov=16;
  y53=7;
  di=1+5;
  p=am;
  us=l;

  while (l<=am-1) {
      if (!(!(l%2==0))) {
          if (od>0) {
              od -= 1;
              r = r + 1;
          }
      }
      else {
          if (r>0) {
              r--;
              od++;
          }
      }
      y53 += r;
      l = l + 1;
      di = di+(l%2);
      ov++;
      p += 2;
      us = us+(l%2);
      y53 = y53 + ov;
  }

}
