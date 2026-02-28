int main1(int a,int m,int q){
  int z, i, v;

  z=22;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant z == 22;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v == 0 || v == \at(q, Pre);
  loop invariant i == 0 && z == 22 && q == \at(q, Pre) && m == \at(m, Pre) && a == \at(a, Pre) && (v == \at(q, Pre) || v == 0);
  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((i%8)==0) {
          v = v-v;
      }
  }

}
