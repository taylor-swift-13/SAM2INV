int main1(int k,int q){
  int j, v, t;

  j=(k%18)+18;
  v=0;
  t=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == k + (v*(v-1))/2;
  loop invariant v <= j;
  loop invariant 0 <= v;
  loop invariant j == (k % 18) + 18;
  loop invariant t == k + v*(v - 1)/2 && j >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant j == (\at(k, Pre) % 18) + 18;
  loop invariant t == \at(k, Pre) + v*(v-1)/2;
  loop invariant q == \at(q,Pre);
  loop invariant t == \at(k, Pre) + (v*(v-1))/2;
  loop assigns t, v;
*/
while (v<j) {
      t = t+v;
      v = v+1;
  }

}
