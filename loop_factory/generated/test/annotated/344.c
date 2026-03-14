int main1(){
  int s2o, a63x, gt, c2, kuj;
  s2o=1;
  a63x=0;
  gt=0;
  c2=0;
  kuj=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gt == a63x;
  loop invariant c2 == gt*(gt+1)/2;
  loop invariant c2 == a63x * (a63x + 1) / 2;
  loop invariant a63x == gt;
  loop invariant s2o == 1;
  loop assigns a63x, gt, c2;
*/
while (gt<s2o) {
      gt = gt + 1;
      a63x++;
      c2 = c2 + gt;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a63x <= gt;
  loop invariant kuj >= 0;
  loop invariant gt == a63x;
  loop invariant c2 >= a63x * (a63x + 1) / 2;
  loop invariant kuj == 2;
  loop invariant c2 >= 0;
  loop invariant kuj >= 2;
  loop invariant c2 >= 1;
  loop assigns c2, kuj, gt;
*/
while (1) {
      if (!(a63x+1<=gt)) {
          break;
      }
      c2 += kuj;
      kuj = kuj+gt-a63x;
      gt = (a63x+1)-1;
  }
}