int main1(int k){
  int ga, vp, os, l6, i7l, ggsw;
  ga=k*2;
  vp=0;
  os=0;
  l6=0;
  i7l=(k%18)+5;
  ggsw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ggsw == (k * 2) * (((\at(k,Pre) % 18) + 5) - i7l);
  loop invariant os  == (k * k) * (((\at(k,Pre) % 18) + 5) - i7l);
  loop invariant l6  == (k * k) * (((\at(k,Pre) % 18) + 5) - i7l);
  loop invariant vp  == (k * k) * (((\at(k,Pre) % 18) + 5) - i7l);
  loop invariant os == (k*k) * (((\at(k, Pre) % 18) + 5) - i7l) &&
                   l6 == (k*k) * (((\at(k, Pre) % 18) + 5) - i7l) &&
                   vp == (k*k) * (((\at(k, Pre) % 18) + 5) - i7l);
  loop invariant ga == 2 * k;
  loop invariant i7l <= ((\at(k, Pre) % 18) + 5);
  loop invariant os == (((k % 18) + 5) - i7l) * (k * k);
  loop invariant l6 == (((k % 18) + 5) - i7l) * (k * k);
  loop invariant vp == (((k % 18) + 5) - i7l) * (k * k);
  loop invariant ggsw == (((k % 18) + 5) - i7l) * ga;
  loop assigns os, l6, i7l, ggsw, vp;
*/
while (i7l>0) {
      os = os+k*k;
      l6 = l6+k*k;
      i7l -= 1;
      ggsw += ga;
      vp = vp+k*k;
  }
}