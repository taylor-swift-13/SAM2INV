int main1(int f){
  int we7f, uk, je, w;
  we7f=(f%32)+9;
  uk=0;
  je=we7f;
  w=f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant je + w == \at(f, Pre) + we7f;
  loop invariant we7f == (\at(f, Pre) % 32) + 9;
  loop invariant f == \at(f, Pre) + uk * we7f;
  loop invariant (we7f >= 0 ==> 0 <= uk && uk <= we7f) && (we7f < 0 ==> uk == 0);
  loop assigns uk, je, w, f;
*/
while (1) {
      if (!(uk < we7f)) {
          break;
      }
      uk += 1;
      if (je >= f) {
          je -= f;
          w += f;
      }
      f = f + we7f;
  }
}