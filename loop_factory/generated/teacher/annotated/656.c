int main1(int k,int n){
  int v, c, t, i, q;

  v=k;
  c=0;
  t=0;
  i=c;
  q=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k;
  loop invariant k == \at(k, Pre);
  loop invariant t >= 0;
  loop invariant t % 5 == 0;
  loop invariant v == \at(k, Pre);
  loop invariant i == 0 || i + t == v + 5;
  loop invariant t % 5 == 0 && t >= 0 && ((i == 0 && t == 0) || (i + t == v + 5));
  loop invariant (t == 0) ==> (i == 0);
  loop invariant (t != 0) ==> (i == v - t + 5);
  loop assigns i, t;
*/
while (1) {
      i = v-t;
      t = t+1;
      t = t+4;
  }

}
