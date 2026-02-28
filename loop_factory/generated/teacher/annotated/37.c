int main1(int m,int p){
  int d, i, v;

  d=31;
  i=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i && i <= d;
  loop invariant d == 31;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant i >= 0;
  loop invariant i <= d;
  loop invariant i == 0 ==> v == -5;
  loop invariant i > 0 ==> v % 2 == 0;
  loop assigns v, i;
*/
while (i<d) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

}
