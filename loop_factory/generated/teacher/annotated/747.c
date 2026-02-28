int main1(int a,int k,int n,int q){
  int b, j, e;

  b=a-8;
  j=0;
  e=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;

  loop invariant b == a - 8;
  loop invariant a == \at(a, Pre);
  loop invariant e >= q;
  loop invariant (e - q) % 3 == 0;
  loop invariant ((e - q) % 3) == 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns e;
*/
while (1) {
      e = e+2;
      if ((j%8)==0) {
          e = e+j;
      }
      e = e+1;
  }

}
