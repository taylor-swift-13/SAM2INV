int main1(int a,int p){
  int q, c, v;

  q=p-2;
  c=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == p - 2;
  loop invariant c == 0;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= a;
  loop invariant (v - a) % 3 == 0;
  loop invariant ((v - a) % 3) == 0;
  loop invariant q == \at(p, Pre) - 2;
  loop assigns v;
*/
while (1) {
      v = v+3;
      if (q<p+2) {
          v = v+c;
      }
      else {
          v = v+1;
      }
  }

}
