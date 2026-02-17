int main1(int k,int m,int p){
  int l, i, v;

  l=56;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant ( (i == 0) ==> (v == m) ) &&
                 ( (i > 0) ==> (v == 6) ) &&
                 (0 <= i && i <= l);
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant p == \at(p, Pre);
   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      if (i+6<=m+l) {
          v = v-v;
      }
      v = v+i;
      v = v-v;
      v = v+6;
      i = i+1;
  }

}