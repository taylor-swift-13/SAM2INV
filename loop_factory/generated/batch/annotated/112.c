int main1(int a){
  int y, i, o;

  y=a-10;
  i=0;
  o=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant y == a - 10;
  loop invariant (y >= 0) ==> (i <= y);
  loop invariant a == \at(a, Pre);
  loop invariant y == \at(a, Pre) - 10;
  loop assigns i;
*/
while (i<y) {
      i = i+1;
  }

}
