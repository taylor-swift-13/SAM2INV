int main1(int a){
  int b, u, i;

  b=59;
  u=0;
  i=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant 0 <= u;
  loop invariant u <= b;
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= u <= b;
  loop invariant b == 59;
  loop assigns i, u;
*/
while (u<b) {
      i = i-i;
      u = u+1;
  }

}
