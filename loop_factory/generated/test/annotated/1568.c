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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant od + r == 6;
  loop invariant di == 6 + (l - 1) / 2;
  loop invariant ov == l + 14;
  loop invariant l >= 2;
  loop invariant r >= 0;
  loop invariant od >= 0;
  loop invariant y53 >= 7;
  loop invariant us <= l;
  loop invariant p == am + 2*(l - 2);
  loop invariant p - 2*ov == -31;
  loop invariant us >= 2;
  loop assigns od, r, y53, l, di, ov, p, us;
*/
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