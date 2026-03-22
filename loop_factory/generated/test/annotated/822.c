int main1(int t,int m){
  int n6c, c1;
  n6c=47;
  c1=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n6c == 47) ==> (t == \at(t,Pre));
  loop invariant c1 == 1;
  loop invariant t >= \at(t, Pre);
  loop invariant n6c == 47 || n6c == 2;
  loop invariant m == \at(m, Pre);
  loop invariant t - \at(t, Pre) <= 1;
  loop invariant ((n6c == 47 && t == \at(t, Pre)) ||
                  (n6c == (3 * c1 - 1) && t == \at(t, Pre) + c1));
  loop assigns t, n6c;
*/
while (c1*3<=n6c) {
      t += c1;
      n6c = (c1*3)-1;
  }
}