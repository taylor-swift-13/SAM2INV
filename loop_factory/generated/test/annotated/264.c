int main1(int i){
  int a6cd, me, o, so5, u;
  a6cd=i+7;
  me=0;
  o=29;
  so5=1;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant so5 == me + 1;
  loop invariant me == u;
  loop invariant 0 <= o;
  loop invariant o <= 29;
  loop invariant so5 >= 1;
  loop assigns me, o, so5, u;
*/
for (; o>0&&so5<=a6cd; me = me + 1) {
      if (o>so5) {
          o = o - so5;
      }
      else {
          o = 0;
      }
      so5 = so5 + 1;
      u = u + 1;
  }
}