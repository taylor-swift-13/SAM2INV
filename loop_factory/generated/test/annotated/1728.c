int main1(int u){
  int li, jc3, e11p;
  li=u;
  jc3=-4204;
  e11p=li;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e11p - \at(u,Pre) >= 0;
  loop invariant li == \at(u, Pre);
  loop invariant jc3 == -4204 + (e11p - li)*(li - 2) + ((e11p - li)*(e11p - li - 1))/2;
  loop invariant u == \at(u, Pre) * (1 + (e11p - li)) + ((e11p - li) * (e11p - li + 1)) / 2;
  loop assigns jc3, e11p, u;
*/
while (jc3<=-8) {
      jc3 = (jc3+e11p)+(-(2));
      e11p += 1;
      u = u + e11p;
  }
}