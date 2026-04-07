int main1(){
  int ef3, u, mt, c, i6;
  ef3=67;
  u=0;
  mt=6;
  c=0;
  i6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mt * i6 + c == u * ef3;
  loop invariant 0 <= c;
  loop invariant c < mt;
  loop invariant 0 <= u;
  loop invariant u <= ef3;
  loop invariant i6 >= 0;
  loop invariant mt > 0;
  loop assigns i6, c, u;
*/
while (u < ef3) {
      i6 = i6 + (c + ef3) / mt;
      c = (c + ef3) % mt;
      u = u + 1;
  }
}