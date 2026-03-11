int main1(){
  int v77, o, e, uv;
  v77=1*3;
  o=0;
  e=v77;
  uv=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 0;
  loop invariant v77 >= o;
  loop invariant uv >= 2;
  loop invariant e > 0;
  loop invariant v77 <= 3;
  loop invariant ((uv - 2) % e) == 0;
  loop assigns uv, v77;
*/
while (o+1<=v77) {
      uv = uv + e;
      v77 = (o+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v77 >= 0;
  loop invariant v77 <= 3;
  loop assigns v77;
*/
for (; v77>0; v77--) {
  }
}