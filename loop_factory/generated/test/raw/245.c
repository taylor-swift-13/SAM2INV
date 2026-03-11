int main1(int m,int j){
  int ek, vj, yae, mb0, rc;

  ek=21;
  vj=3;
  yae=0;
  mb0=j;
  rc=0;

  while (yae<ek) {
      if (rc<ek) {
          mb0 = yae;
      }
      rc = rc + 1;
      yae++;
  }

  while (mb0-1>=0) {
      vj = vj+ek*mb0;
      j += vj;
      mb0 = mb0 + 1;
  }

}
