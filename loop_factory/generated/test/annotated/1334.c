int main1(int v,int g){
  int s, j;
  s=0;
  j=(v%28)+10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == ((\at(v, Pre) % 28) + 10) - ((s * (s - 1)) / 2);
  loop invariant v == \at(v, Pre) + ((s + 1) / 2);
  loop invariant s >= 0;
  loop assigns j, s, v;
*/
while (j>s) {
      j = j - s;
      s = (1)+(s);
      v = v+(s%2);
  }
}