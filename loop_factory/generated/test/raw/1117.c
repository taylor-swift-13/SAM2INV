int main1(int q){
  int y, b5, gdz, t, rc, eu;

  y=q;
  b5=1;
  gdz=0;
  t=0;
  rc=b5;
  eu=q+1;

  while (1) {
      if (!(t<=y-1)) {
          break;
      }
      gdz = gdz + q;
      rc = rc + b5;
      t += 1;
  }

  while (rc-gdz>0) {
      y = y+t*rc;
      eu = eu + rc;
      gdz = 0;
  }

}
