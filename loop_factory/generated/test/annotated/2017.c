int main1(int p){
  int o0b3, i2, o, bvj;
  o0b3=(p%21)+13;
  i2=0;
  o=i2;
  bvj=o0b3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o0b3 == ((\at(p, Pre) % 21) + 13);
  loop invariant bvj == o0b3 + 2 * o;
  loop invariant p == \at(p, Pre);
  loop invariant (o == 0 && i2 == 0) || (o == 1 && i2 == o0b3);
  loop invariant (i2 == 0) <==> (o == 0);
  loop assigns p, o, bvj, i2;
*/
while (i2 < o0b3) {
      p = p + i2;
      o = o + 1;
      bvj += 2;
      i2 = o0b3;
  }
}