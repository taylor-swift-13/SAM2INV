int main1(){
  int gl, ch6, qf, h5pg, ou, nei, wwc, cn, e, da;

  gl=1;
  ch6=0;
  qf=1;
  h5pg=1;
  ou=0;
  nei=3;
  wwc=0;
  cn=gl;
  e=gl;
  da=ch6;

  while (ch6<gl) {
      if (ch6%3==0) {
          if (qf>0) {
              qf = qf - 1;
              ou = ou + 1;
          }
      }
      else {
          if (qf<nei) {
              qf += 1;
              h5pg = h5pg + 1;
          }
      }
      da += h5pg;
      e += 1;
      wwc++;
      cn += 1;
      nei++;
      ch6 += 1;
  }

}
