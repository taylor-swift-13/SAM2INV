int main1(int y,int e){
  int ex, iji, s7v, w;
  ex=e;
  iji=0;
  s7v=2;
  w=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ex == \at(e, Pre);
  loop invariant s7v == 2 + 3 * iji;
  loop invariant w == 5 + 3 * iji;
  loop invariant 0 <= iji;
  loop invariant (ex >= 0) ==> (iji <= ex) && ex == e;
  loop assigns iji, s7v, w;
*/
while (1) {
      if (!(iji<ex)) {
          break;
      }
      s7v = s7v + 3;
      w = w + 3;
      iji++;
  }
}