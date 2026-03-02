int main1(int a,int p){
  int b, j, o;

  b=25;
  j=2;
  o=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 25;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant o >= 25;

  loop assigns o;
*/
while (1) {
      o = o+3;
      o = o+o;
  }

}
