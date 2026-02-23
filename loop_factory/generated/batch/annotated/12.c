int main1(int a,int p){
  int s, t, v, z, n, i;

  s=a-9;
  t=0;
  v=p;
  z=p;
  n=p;
  i=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant s == a - 9;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant ((p >= 0) ==> (0 <= v && v <= p) && (0 <= z && z <= p));

  loop assigns v, z;
*/
while (v!=0&&z!=0) {
      if (v>z) {
          v = v-z;
      }
      else {
          z = z-v;
      }
  }

}
