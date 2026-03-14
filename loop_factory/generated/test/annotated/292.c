int main1(int c,int l){
  int cxa3, och, vb4, c4;
  cxa3=(l%25)+12;
  och=0;
  vb4=l;
  c4=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vb4 == \at(l, Pre) + och;
  loop invariant cxa3 == \at(l, Pre) % 25 + 12;
  loop invariant 8 <= c4 <= 8 + och;
  loop assigns l, vb4, c4, och;
*/
while (1) {
      l = vb4+c4+c;
      vb4++;
      if (l+5<cxa3) {
          c4++;
      }
      och += 1;
      if (och>=cxa3) {
          break;
      }
  }
}