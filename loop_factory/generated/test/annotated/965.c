int main1(int a,int j){
  int l, li;
  l=a;
  li=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (li % 6) == 0;
  loop invariant l == \at(a, Pre);
  loop invariant li >= 0;
  loop invariant 6*(a - \at(a, Pre)) == li * j;
  loop invariant (a - j * (li/6) == \at(a, Pre)) &&
                 (li % 6 == 0) &&
                 (l == \at(a, Pre)) &&
                 (j == \at(j, Pre));
  loop assigns a, li;
*/
for (; li<=l-6; li += 6) {
      a += j;
  }
}