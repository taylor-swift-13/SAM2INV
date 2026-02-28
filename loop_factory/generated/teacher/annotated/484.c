int main1(int k,int p){
  int n, o, w, v;

  n=k+3;
  o=2;
  w=p;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == p + 6*(o - 2);
  loop invariant n == k + 3;
  loop invariant o >= 2;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant w == \at(p, Pre) + 6*(o - 2);

  loop assigns w, o;
*/
while (1) {
      if (o>=n) {
          break;
      }
      w = w+3;
      o = o+1;
      w = w+3;
  }

}
