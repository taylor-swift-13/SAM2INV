int main1(int a){
  int l3o, t, fkv;
  l3o=a*5;
  t=0;
  fkv=l3o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fkv == l3o + t;
  loop invariant l3o == 5 * a;
  loop invariant t >= 0;
  loop assigns fkv, t;
*/
while (t<=l3o-1) {
      fkv = fkv + 1;
      t += 1;
  }
}