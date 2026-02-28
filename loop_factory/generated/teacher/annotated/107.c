int main1(int b){
  int m, i, h;

  m=b;
  i=0;
  h=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(b, Pre);
  loop invariant 0 <= i;
  loop invariant b == \at(b, Pre);
  loop invariant i >= 0;
  loop invariant (m < 0) || i <= m;
  loop invariant (m < 0) || (i <= m);
  loop invariant m == b;

  loop assigns i;
*/
while (i<=m-1) {
      i = i+1;
  }

}
