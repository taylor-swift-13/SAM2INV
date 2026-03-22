int main1(){
  int vpo, w, zk9f, ga, e, wn6, t;

  vpo=1+6;
  w=0;
  zk9f=-3;
  ga=w;
  e=vpo;
  wn6=vpo;
  t=w;

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
