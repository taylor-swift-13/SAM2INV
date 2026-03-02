int main1(int k,int p){
  int l, j, i, v;

  l=p;
  j=0;
  i=j;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i % 4 == 0;
  loop invariant v <= 0;
  loop invariant l == p;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l == p && i % 4 == 0 && i >= 0 && v <= 0;
  loop invariant i >= 0 && v <= 0 && i + v >= 0;
  loop invariant i % 4 == 0 && p == \at(p, Pre) && k == \at(k, Pre) && l == \at(p, Pre);
  loop invariant i % 4 == 0 && i >= 0;
  loop invariant v <= 0 && l == \at(p, Pre) && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant v <= 0 && l == p && p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant v <= 0 && i >= 0;
  loop invariant i >= 4 * (-v) && p == \at(p, Pre) && k == \at(k, Pre) && l == \at(p, Pre);
  loop invariant l == \at(p, Pre);
  loop invariant p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant i >= 0;
  loop assigns i, v;
*/
while (1) {
      i = i+1;
      v = v-1;
      i = i*4;
  }

}
