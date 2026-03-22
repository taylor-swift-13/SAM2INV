int main1(){
  int vpo, w, zk9f, ga, e, wn6, t;
  vpo=1+6;
  w=0;
  zk9f=-3;
  ga=w;
  e=vpo;
  wn6=vpo;
  t=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zk9f <= 0;
  loop invariant ga >= 0;
  loop invariant t >= 0;
  loop invariant t % 2 == 0;
  loop invariant e >= 7;
  loop invariant wn6 == 7;
  loop invariant vpo == 7;
  loop invariant e % 7 == 0;
  loop invariant ga % 3 == 0;
  loop invariant zk9f % 3 == 0;
  loop assigns zk9f, wn6, ga, e, t;
*/
while (zk9f!=ga) {
      if (zk9f>ga) {
          zk9f -= ga;
          wn6 = wn6 + e;
      }
      else {
          ga -= zk9f;
          e = e + wn6;
      }
      t = t + e;
      t = t*2;
  }
}