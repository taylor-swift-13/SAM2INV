int main1(){
  int p, b, edz, dbp, mwwd, o;

  p=1*5;
  b=0;
  edz=(1%40)+2;
  dbp=0;
  mwwd=p;
  o=p;

  while (edz!=dbp) {
      dbp = edz;
      mwwd += b;
      edz = (edz+p/edz)/2;
  }

  while (edz!=mwwd) {
      mwwd = edz;
      edz = (edz+o/edz)/2;
      dbp = dbp + edz;
  }

}
