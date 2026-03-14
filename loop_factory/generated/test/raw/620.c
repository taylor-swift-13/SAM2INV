int main1(){
  int so, lyv6, oc, r6fr, qv;

  so=1;
  lyv6=0;
  oc=4;
  r6fr=0;
  qv=0;

  while (lyv6<so) {
      r6fr = r6fr + 1;
      qv = qv + 1;
      if (r6fr>=5) {
          r6fr = r6fr - 5;
          oc = oc + 1;
      }
      lyv6 += 1;
  }

}
