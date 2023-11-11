FROM minizinc/minizinc:latest

WORKDIR C:\Users\utente\Videos\Final_Project\CDMO

COPY . .

RUN apt-get update
RUN apt-get install -y python3.10
RUN apt-get install -y python3-pip
RUN apt-get install -y glpk-utils
RUN python3 -m pip install -r requirements.txt
RUN apt-get install -y z3
RUN apt-get install -y cvc4
RUN apt-get install -y dos2unix
RUN dos2unix SMT/src/binary.sh \
    && chmod +x SMT/src/binary.sh \
    && dos2unix SMT/src/linear.sh \
   && chmod +x SMT/src/linear.sh \
   && apt-get install -y bash coreutils



CMD python3 main.py -a smtlib -n 1
