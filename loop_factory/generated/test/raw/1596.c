int main1(int a){
  int k, bb, ew, jm, tl, w6, nl7i, kad;

  k=75;
  bb=k;
  ew=16;
  jm=0;
  tl=1;
  w6=0;
  nl7i=a;
  kad=0;

  while (ew>0&&bb<k) {
      if (ew<=tl) {
          w6 = ew;
      }
      else {
          w6 = tl;
      }
      ew = ew - w6;
      tl += 1;
      bb++;
      jm = jm + w6;
      if (kad*kad<=k+5) {
          kad = nl7i*nl7i;
      }
      nl7i += bb;
      a = a + w6;
      nl7i += bb;
  }

}
